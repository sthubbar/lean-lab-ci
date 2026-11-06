import LeanLab.LiuWang2002.Checkpoint368

/-!
Composite witnesses for bounded primorial certificates.
Source Schoenfeld page 356, display 5.1 star, derived proof data.
An unmarked integer is included even if it is composite.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task368
open Task352

/-- A zero mark retains the integer. Every positive mark must be a
proper divisor of the next integer. Derived data for page 356,
display 5.1 star. -/
def coverCheck : ℕ → List ℕ → Bool
  | _, [] => true
  | n, d :: ds =>
    match n + 1 with
    | 0 => (decide (d = 0) || decide (2 ≤ d ∧ d < 0 ∧ 0 % d = 0)) && coverCheck 0 ds
    | m + 1 => (decide (d = 0) || decide (2 ≤ d ∧ d < m + 1 ∧ (m + 1) % d = 0)) &&
        coverCheck (m + 1) ds

/-- The product of all integers retained by zero marks. Derived upper
product data for page 356, display 5.1 star. -/
def coverProduct : ℕ → List ℕ → ℕ
  | _, [] => 1
  | n, d :: ds =>
    match n + 1 with
    | 0 => if d = 0 then 0 * coverProduct 0 ds else coverProduct 0 ds
    | m + 1 => if d = 0 then (m + 1) * coverProduct (m + 1) ds
        else coverProduct (m + 1) ds

/-- The forced integer implementation has exactly the original
one step divisor predicate. Derived identity for page 356,
display 5.1 star. -/
theorem coverCheck_step (n d : ℕ) (ds : List ℕ) :
    coverCheck n (d :: ds) =
      ((decide (d = 0) || decide (2 ≤ d ∧ d < n + 1 ∧ (n + 1) % d = 0)) &&
        coverCheck (n + 1) ds) := by
  cases h : n + 1 <;> simp only [coverCheck, h]

/-- The forced integer implementation retains exactly the marked
integers. Derived identity for page 356, display 5.1 star. -/
theorem coverProduct_step (n d : ℕ) (ds : List ℕ) :
    coverProduct n (d :: ds) =
      if d = 0 then (n + 1) * coverProduct (n + 1) ds else coverProduct (n + 1) ds := by
  cases h : n + 1 <;> simp only [coverProduct, h]

/-- Checked proper divisors justify every omitted factor. Unmarked
integers give an upper product regardless of primality.
Derived transfer for page 356, display 5.1 star. -/
theorem cover_primorial (ds : List ℕ) (n : ℕ) (hc : coverCheck n ds = true) :
    primorial (n + ds.length) ≤ primorial n * coverProduct n ds := by
  induction ds generalizing n with
  | nil => simp [coverProduct]
  | cons d ds ih =>
    simp only [coverCheck_step, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
    have hh := ih (n + 1) hc.2
    have he : n + (d :: ds).length = (n + 1) + ds.length := by simp; omega
    rw [he]
    apply hh.trans
    by_cases hd : d = 0
    · simp only [coverProduct_step, if_pos hd]
      have hp : primorial (n + 1) ≤ primorial n * (n + 1) := by
        rw [primorial_next]
        split_ifs
        · exact le_rfl
        · simp only [mul_one]
          exact Nat.le_mul_of_pos_right _ (by omega)
      simpa only [mul_assoc] using Nat.mul_le_mul_right (coverProduct (n + 1) ds) hp
    · have hf := hc.1.resolve_left hd
      have hn : ¬ (n + 1).Prime := Nat.not_prime_of_dvd_of_lt
        (Nat.dvd_of_mod_eq_zero hf.2.2) hf.1 hf.2.1
      have hp : primorial (n + 1) = primorial n := by
        rw [primorial_next, if_neg (fun h => hn (Nat.prime_def_minFac.mpr h)), mul_one]
      simp only [coverProduct_step, if_neg hd, hp]
      exact le_rfl

/-- The checked upper product also bounds the exact interval product.
Derived transfer for page 356, display 5.1 star. -/
theorem segment_le_cover (ds : List ℕ) (n : ℕ) (hc : coverCheck n ds = true) :
    segmentProduct ds.length n ≤ coverProduct n ds := by
  have h := cover_primorial ds n hc
  rw [primorial_segment] at h
  exact Nat.le_of_mul_le_mul_left h (primorial_pos n)

/-- Check composite witnesses, interval bounds and terminal bounds
from explicit states. Derived executable data for page 356,
display 5.1 star. -/
def coverCheckpointCheck (S n r : ℕ) : List (List ℕ × ℕ) → Bool
  | [] => true
  | (ds, s) :: rest =>
    match n + ds.length with
    | 0 => coverCheck n ds &&
      decide (r * coverProduct n ds * 25 < S * 68) &&
      decide (r * coverProduct n ds * 25 ^ ds.length ≤ s * 68 ^ ds.length) &&
      coverCheckpointCheck S 0 s rest
    | m + 1 => coverCheck n ds &&
      decide (r * coverProduct n ds * 25 < S * 68) &&
      decide (r * coverProduct n ds * 25 ^ ds.length ≤ s * 68 ^ ds.length) &&
      coverCheckpointCheck S (m + 1) s rest

/-- Forcing the next integer preserves both ratio bounds and the
recursive checkpoint predicate. Derived identity for page 356,
display 5.1 star. -/
theorem coverCheckpointCheck_step (S n r s : ℕ) (ds : List ℕ)
    (rest : List (List ℕ × ℕ)) :
    coverCheckpointCheck S n r ((ds, s) :: rest) =
      (coverCheck n ds &&
      decide (r * coverProduct n ds * 25 < S * 68) &&
      decide (r * coverProduct n ds * 25 ^ ds.length ≤ s * 68 ^ ds.length) &&
      coverCheckpointCheck S (n + ds.length) s rest) := by
  cases h : n + ds.length <;> simp only [coverCheckpointCheck, h]

/-- A successful composite witness checkpoint list gives the exact
integer certificate throughout its covered interval.
Derived transfer for page 356, display 5.1 star. -/
theorem coverCheckpoint_sound (cs : List (List ℕ × ℕ)) (S n r : ℕ)
    (hi : primorial n * 25 ^ n * S ≤ r * 68 ^ n)
    (hc : coverCheckpointCheck S n r cs = true) :
    ∀ m : ℕ, n < m → m ≤ n + (cs.map (fun c => c.1.length)).sum →
      primorial m * 25 ^ m < 68 ^ m := by
  induction cs generalizing n r with
  | nil => simp only [List.map_nil, List.sum_nil, Nat.add_zero]; omega
  | cons c cs ih =>
    obtain ⟨ds, s⟩ := c
    simp only [coverCheckpointCheck_step, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hp := segment_le_cover ds n hc.1.1.1
    have hr : r * segmentProduct ds.length n * 25 < S * 68 :=
      (Nat.mul_le_mul_right 25 (Nat.mul_le_mul_left r hp)).trans_lt hc.1.1.2
    have ht : r * segmentProduct ds.length n * 25 ^ ds.length ≤ s * 68 ^ ds.length :=
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left r hp)).trans hc.1.2
    intro m hm hm'
    by_cases hk : m ≤ n + ds.length
    · exact checkpoint_range ds.length n r S hi hr m hm hk
    · apply ih (n + ds.length) s (checkpoint_next ds.length n r s S hi ht) hc.2 m (by omega)
      simp only [List.map_cons, List.sum_cons] at hm'
      omega

/-- The last explicit terminal state supplies the next file's exact
invariant. Derived transfer for page 356, display 5.1 star. -/
theorem coverCheckpoint_terminal (cs : List (List ℕ × ℕ)) (S n r : ℕ)
    (hi : primorial n * 25 ^ n * S ≤ r * 68 ^ n)
    (hc : coverCheckpointCheck S n r cs = true) :
    primorial (n + (cs.map (fun c => c.1.length)).sum) *
      25 ^ (n + (cs.map (fun c => c.1.length)).sum) * S ≤
      (cs.getLast?.getD ([], r)).2 * 68 ^ (n + (cs.map (fun c => c.1.length)).sum) := by
  induction cs generalizing n r with
  | nil => simpa using hi
  | cons c cs ih =>
    obtain ⟨ds, s⟩ := c
    simp only [coverCheckpointCheck_step, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hp := segment_le_cover ds n hc.1.1.1
    have ht : r * segmentProduct ds.length n * 25 ^ ds.length ≤ s * 68 ^ ds.length :=
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left r hp)).trans hc.1.2
    have hh := ih (n + ds.length) s (checkpoint_next ds.length n r s S hi ht) hc.2
    cases cs with
    | nil => simpa using hh
    | cons c cs => simpa [Nat.add_assoc, List.getLast?_cons] using hh

/-- A nonempty instance omits composite 4 using divisor 2 and retains
primes 2 and 3. Derived instance for page 356, display 5.1 star. -/
theorem cover_instance : coverCheck 1 [0, 0, 2] = true ∧
    coverProduct 1 [0, 0, 2] = 6 ∧ segmentProduct 3 1 = 6 := by
  decide +kernel

end LeanLab.LiuWang2002.Task368
#print axioms LeanLab.LiuWang2002.Task368.cover_primorial
#print axioms LeanLab.LiuWang2002.Task368.segment_le_cover
#print axioms LeanLab.LiuWang2002.Task368.coverCheckpoint_sound
#print axioms LeanLab.LiuWang2002.Task368.coverCheckpoint_terminal
#print axioms LeanLab.LiuWang2002.Task368.cover_instance

namespace LeanLab.LiuWang2002.Task368
/-- Explicit endpoint and state equalities keep closed primorials
opaque during elaboration. Derived transfer for page 356,
display 5.1 star. -/
theorem coverCheckpoint_terminal_at (cs : List (List ℕ × ℕ)) (S n r N s : ℕ)
    (hN : n + (cs.map (fun c => c.1.length)).sum = N)
    (hs : (cs.getLast?.getD ([], r)).2 = s)
    (hi : primorial n * 25 ^ n * S ≤ r * 68 ^ n)
    (hc : coverCheckpointCheck S n r cs = true) :
    primorial N * 25 ^ N * S ≤ s * 68 ^ N := by
  have h := coverCheckpoint_terminal cs S n r hi hc
  rwa [hN, hs] at h

/-- The explicit final integer avoids matching a closed primorial
against an unevaluated sum of list lengths. Derived transfer for
page 356, display 5.1 star. -/
theorem coverCheckpoint_sound_at (cs : List (List ℕ × ℕ)) (S n r N : ℕ)
    (hN : n + (cs.map (fun c => c.1.length)).sum = N)
    (hi : primorial n * 25 ^ n * S ≤ r * 68 ^ n)
    (hc : coverCheckpointCheck S n r cs = true) :
    ∀ m : ℕ, n < m → m ≤ N → primorial m * 25 ^ m < 68 ^ m := by
  have h := coverCheckpoint_sound cs S n r hi hc
  rwa [hN] at h
end LeanLab.LiuWang2002.Task368
#print axioms LeanLab.LiuWang2002.Task368.coverCheckpoint_terminal_at
#print axioms LeanLab.LiuWang2002.Task368.coverCheckpoint_sound_at

#print axioms LeanLab.LiuWang2002.Task368.coverCheck_step
#print axioms LeanLab.LiuWang2002.Task368.coverProduct_step
#print axioms LeanLab.LiuWang2002.Task368.coverCheckpointCheck_step
