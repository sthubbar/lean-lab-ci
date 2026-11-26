/-
P0088 page 7 before display 27. The finite kernel primitive and weighted window.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.KernelMass687
import LeanLab.KumchevLiu2007.Kernel634Base
import LeanLab.KumchevLiu2007.KernelSumPieces1122

namespace LeanLab.KumchevLiu2007.Task687
open Real MeasureTheory LeanLab.KumchevLiu2007 KernelSumSplit1122
open scoped BigOperators Topology

/-- The kernel is even in its integer index. -/
theorem Kb_even (b : ℝ) (k : ℤ) : Kb b (-k) = Kb b k := by
  by_cases hk : k = 0
  · subst k; simp
  · simp [Kb, hk, mul_neg, Real.sin_neg, neg_div_neg_eq]

/-- A finite primitive of the paper kernel on the integer line. -/
noncomputable def kernelPrimitive (b : ℝ) (k : ℤ) : ℝ :=
  if 0 ≤ k then kernelMass b k.toNat / 2 else -kernelMass b (-k-1).toNat / 2

/-- The increment of the finite primitive is the paper kernel. -/
theorem kernelPrimitive_step (b : ℝ) (k : ℤ) :
    kernelPrimitive b (k+1) - kernelPrimitive b k = Kb b (k+1) := by
  by_cases hk : 0 ≤ k
  · have hkp : 0 ≤ k+1 := by omega
    have he : (k+1).toNat = k.toNat+1 := by omega
    have he' : (k+1) = (k.toNat+1 : ℕ) := by omega
    simp only [kernelPrimitive, ite_eq_left hk, ite_eq_left hkp, he]
    rw [kernelMass_succ, he']
    ring
  · by_cases hkm : k = -1
    · subst k
      norm_num [kernelPrimitive, kernelMass_zero, Kb]
      ring
    · have hkp : ¬0 ≤ k+1 := by omega
      have he : (-k-1).toNat = (- (k+1)-1).toNat+1 := by omega
      have he' : -(k+1) = ((- (k+1)-1).toNat+1 : ℕ) := by omega
      simp only [kernelPrimitive, ite_eq_right hk, ite_eq_right hkp, he]
      rw [kernelMass_succ]
      have hkb : Kb b ((- (k+1)-1).toNat+1 : ℕ) = Kb b (k+1) := by
        rw [← he', Kb_even]
      rw [hkb]
      ring

/-- The finite primitive has uniform size at most four. -/
theorem kernelPrimitive_bounded (b : ℝ) (k : ℤ) (hb : 0 < b) (hb' : b ≤ 1/2) :
    |kernelPrimitive b k| ≤ 4 := by
  unfold kernelPrimitive
  split_ifs with hk <;> simp only [abs_div, abs_neg, abs_two]
  · linarith [kernelMass_bounded b k.toNat hb hb']
  · linarith [kernelMass_bounded b (-k-1).toNat hb hb']

/-- The primitive decays with its distance from zero. -/
theorem kernelPrimitive_decay (b : ℝ) (k : ℤ) (hb : 0 < b) (hb' : b ≤ 1/2) :
    |kernelPrimitive b k| ≤ 2 / (b * (|(k : ℝ)| + 1)) := by
  by_cases hk : 0 ≤ k
  · have hkR : 0 ≤ (k:ℝ) := by exact_mod_cast hk
    have he : (k.toNat : ℝ) = (k:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk
    unfold kernelPrimitive
    rw [ite_eq_left hk, abs_div, abs_two, abs_of_nonneg hkR]
    have hh := kernelMass_decay b k.toNat hb hb'
    rw [he] at hh
    have hp : 0 ≤ 2/(b*((k:ℝ)+1)) := by positivity
    linarith
  · have hkR : (k:ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    have he : ((-k-1).toNat : ℝ) = -(k:ℝ)-1 := by
      have hh : ((-k-1).toNat : ℤ) = -k-1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast hh
    unfold kernelPrimitive
    rw [ite_eq_right hk, abs_div, abs_neg, abs_two, abs_of_nonpos (by linarith : (k:ℝ) ≤ 0)]
    have hh := kernelMass_decay b (-k-1).toNat hb hb'
    rw [he] at hh
    have hd : -(k:ℝ)-1+1 = -(k:ℝ) := by ring
    rw [hd] at hh
    calc
      _ ≤ (2 / (b * -(k:ℝ))) / 2 := div_le_div_of_nonneg_right hh (by norm_num)
      _ = 1 / (b * -(k:ℝ)) := by ring
      _ ≤ 2 / (b * (-(k:ℝ)+1)) := by
        apply (div_le_div_iff₀ (mul_pos hb (by linarith)) (mul_pos hb (by linarith))).2
        nlinarith [mul_nonneg hb.le (by linarith : 0 ≤ -(k:ℝ)-1)]

/-- The finite primitive has both uniform size and endpoint decay. -/
theorem kernelPrimitive_min_bound (b : ℝ) (k : ℤ) (hb : 0 < b) (hb' : b ≤ 1/2) :
    |kernelPrimitive b k| ≤ 4 * min 1 (1 / (b * (|(k:ℝ)|+1))) := by
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 4)]
  apply le_min
  · simpa using kernelPrimitive_bounded b k hb hb'
  · have hh := kernelPrimitive_decay b k hb hb'
    have he : 2/(b*(|(k:ℝ)|+1)) = 2*(1/(b*(|(k:ℝ)|+1))) := by ring
    rw [he] at hh
    have hp : 0 ≤ 1/(b*(|(k:ℝ)|+1)) := by positivity
    linarith

/-- The kernel sum on any finite consecutive block telescopes. -/
theorem kernel_sum_range (b : ℝ) (s : ℤ) (N : ℕ) :
    ∑ i ∈ Finset.range N, Kb b (s+i) =
      kernelPrimitive b (s+N-1) - kernelPrimitive b (s-1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have hh := kernelPrimitive_step b (s+N-1)
    have he : s+(N:ℤ)-1+1 = s+N := by ring
    rw [he] at hh
    have he' : s+((N+1:ℕ):ℤ)-1 = s+N := by push_cast; ring
    rw [he']
    linarith

/-- Weighted kernel sums obey finite summation by parts. -/
theorem kernel_weighted_range (b : ℝ) (s : ℤ) (w : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ Finset.range (N+1), w i * Kb b (s+i) =
      w N * kernelPrimitive b (s+N) - w 0 * kernelPrimitive b (s-1) -
        ∑ i ∈ Finset.range N, (w (i+1)-w i) * kernelPrimitive b (s+i) := by
  have h := Finset.sum_range_by_parts w (fun i : ℕ => Kb b (s+i)) (N+1)
  simp only [smul_eq_mul, Nat.add_sub_cancel] at h
  simp_rw [kernel_sum_range] at h
  have he (i : ℕ) : s+((i+1:ℕ):ℤ)-1 = s+i := by push_cast; ring
  simp_rw [he, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_range_sub] at h
  calc
    _ = _ := h
    _ = _ := by ring

/-- Weighted finite kernel sums cost endpoint mass plus weight variation. -/
theorem kernel_weighted_range_bound (b : ℝ) (s : ℤ) (w : ℕ → ℝ) (N : ℕ)
    (hb : 0 < b) (hb' : b ≤ 1/2) (hw : ∀ i ≤ N, 0 ≤ w i)
    (hm : ∀ i < N, w (i+1) ≤ w i) (E : ℝ) (_hE : 0 ≤ E)
    (hlo : |kernelPrimitive b (s-1)| ≤ E) (hhi : |kernelPrimitive b (s+N)| ≤ E) :
    |∑ i ∈ Finset.range (N+1), w i * Kb b (s+i)| ≤
      (w N + w 0) * E + 4 * (w 0 - w N) := by
  rw [kernel_weighted_range]
  have hv : |∑ i ∈ Finset.range N, (w (i+1)-w i) * kernelPrimitive b (s+i)| ≤
      4 * (w 0 - w N) := by
    calc
      _ ≤ ∑ i ∈ Finset.range N, |(w (i+1)-w i) * kernelPrimitive b (s+i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range N, 4 * (w i - w (i+1)) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (hm i (Finset.mem_range.mp hi)))]
        have hh := kernelPrimitive_bounded b (s+i) hb hb'
        nlinarith [hm i (Finset.mem_range.mp hi)]
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub']
  calc
    _ ≤ |w N * kernelPrimitive b (s+N) - w 0 * kernelPrimitive b (s-1)| +
      |∑ i ∈ Finset.range N, (w (i+1)-w i) * kernelPrimitive b (s+i)| := by
      simpa only [Real.norm_eq_abs] using
        (norm_sub_le (w N * kernelPrimitive b (s+N) - w 0 * kernelPrimitive b (s-1))
          (∑ i ∈ Finset.range N, (w (i+1)-w i) * kernelPrimitive b (s+i)))
    _ ≤ (w N + w 0) * E + 4 * (w 0 - w N) := by
      have hh := norm_sub_le (w N * kernelPrimitive b (s+N)) (w 0 * kernelPrimitive b (s-1))
      simp only [Real.norm_eq_abs] at hh
      rw [abs_mul, abs_mul, abs_of_nonneg (hw N le_rfl), abs_of_nonneg (hw 0 (Nat.zero_le N))] at hh
      nlinarith [mul_le_mul_of_nonneg_left hlo (hw 0 (Nat.zero_le N)),
        mul_le_mul_of_nonneg_left hhi (hw N le_rfl)]

/-- Moving a primitive endpoint by at most one costs only a fixed constant. -/
theorem kernelPrimitive_near_bound (b r : ℝ) (k : ℤ) (hb : 0 < b) (hb' : b ≤ 1/2)
    (hr : |r-(k:ℝ)| ≤ 1) :
    |kernelPrimitive b k| ≤ 4 * min 1 (1/(b*(|r|+1))) := by
  have hdist : |r| ≤ |(k:ℝ)|+1 := by
    have hh := abs_add_le (r-(k:ℝ)) (k:ℝ)
    have he : r-(k:ℝ)+(k:ℝ) = r := by ring
    rw [he] at hh
    linarith
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 4)]
  apply le_min
  · simpa using kernelPrimitive_bounded b k hb hb'
  · have hh := kernelPrimitive_decay b k hb hb'
    calc
      _ ≤ 2/(b*(|(k:ℝ)|+1)) := hh
      _ ≤ 4/(b*(|r|+1)) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith [mul_nonneg hb.le (abs_nonneg (k:ℝ))]
      _ = _ := by ring

/-- The logarithmic weight varies by at most relative interval length. -/
theorem reciprocal_log_variation (u v : ℝ) (hu : 0 < u) (hu1 : 1 ≤ Real.log u)
    (huv : u ≤ v) :
    1/Real.log u - 1/Real.log v ≤ (v-u)/u := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hlog : Real.log u ≤ Real.log v := Real.log_le_log hu huv
  have hlp : 0 < Real.log u := by linarith
  have hlvp : 0 < Real.log v := by linarith
  have hh := Real.log_le_sub_one_of_pos (div_pos hv hu)
  rw [Real.log_div (ne_of_gt hv) (ne_of_gt hu)] at hh
  have he : 1/Real.log u - 1/Real.log v =
      (Real.log v-Real.log u)/(Real.log u * Real.log v) := by field_simp
  rw [he]
  calc
    _ ≤ Real.log v-Real.log u := by
      apply (div_le_iff₀ (mul_pos hlp hlvp)).2
      have hd : 1 ≤ Real.log u * Real.log v := by nlinarith
      nlinarith
    _ ≤ v/u-1 := hh
    _ = _ := by field_simp

/-- The real window endpoints control the logarithmically weighted kernel sum. -/
theorem inner_window_elementary (X Y b : ℝ) (n m2 : ℕ)
    (hX : 16 ≤ X) (hL : 2 ≤ Real.log X) (hY : 0 < Y) (hYX : Y ≤ X/2)
    (hb : 0 < b) (hb' : b ≤ 1/2) :
    |innerSum X Y b n m2| ≤ 32 * (edgeDecay X Y b n m2 / Real.log X + Y/X) := by
  classical
  let a : ℕ := ⌈X-Y⌉₊
  let z : ℕ := ⌈X⌉₊
  have hX0 : 0 < X := by linarith
  have hXY : 0 ≤ X-Y := by linarith
  have ha : X-Y ≤ (a:ℝ) := Nat.le_ceil _
  have ha' : (a:ℝ) < X-Y+1 := Nat.ceil_lt_add_one hXY
  have hz : X ≤ (z:ℝ) := Nat.le_ceil _
  have hz' : (z:ℝ) < X+1 := Nat.ceil_lt_add_one hX0.le
  have haz : a ≤ z := Nat.ceil_mono (by linarith : X-Y ≤ X)
  have he0 : 0 ≤ edgeDecay X Y b n m2 := KernelSumPieces1122.edgeDecay_nonneg _ _ _ _ _ hb.le
  have hR : 0 ≤ 32 * (edgeDecay X Y b n m2 / Real.log X + Y/X) := by positivity
  by_cases he : a = z
  · unfold innerSum
    rw [Task556d.primeWindow_eq_Ico]
    change |∑ _ ∈ Finset.Ico a z, _| ≤ _
    simp only [he, Finset.Ico_self, Finset.sum_empty, abs_zero]
    exact hR
  let N : ℕ := z-a-1
  have hNz : a+N+1 = z := by dsimp [N]; omega
  have hN : z-a = N+1 := by omega
  have ha0 : 0 < (a:ℝ) := by linarith
  have hlast : (a:ℝ)+(N:ℝ) < X := by
    have hh : (a:ℝ)+(N:ℝ)+1 = (z:ℝ) := by exact_mod_cast hNz
    linarith
  have hloga : Real.log X / 2 ≤ Real.log (a:ℝ) := by
    have hh := Real.log_le_log (by positivity : 0 < X/2) (by linarith : X/2 ≤ (a:ℝ))
    rw [Real.log_div (ne_of_gt hX0) (by norm_num)] at hh
    have h2 : Real.log 2 ≤ 1 := by have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    linarith
  have hloga1 : 1 ≤ Real.log (a:ℝ) := by linarith
  let w : ℕ → ℝ := fun i => 1 / Real.log ((a:ℝ)+i)
  have hwlog (i : ℕ) : 1 ≤ Real.log ((a:ℝ)+i) := by
    have hh := Real.log_le_log ha0 (show (a:ℝ) ≤ (a:ℝ)+i by exact le_add_of_nonneg_right (Nat.cast_nonneg i))
    linarith
  have hw (i : ℕ) : 0 ≤ w i := by dsimp [w]; exact div_nonneg zero_le_one (by linarith [hwlog i])
  have hwL (i : ℕ) : w i ≤ 2/Real.log X := by
    have hh := Real.log_le_log ha0 (show (a:ℝ) ≤ (a:ℝ)+i by exact le_add_of_nonneg_right (Nat.cast_nonneg i))
    dsimp [w]
    apply (div_le_div_iff₀ (by linarith [hwlog i]) (by linarith : 0 < Real.log X)).2
    linarith
  have hwm (i : ℕ) : w (i+1) ≤ w i := by
    dsimp [w]
    apply one_div_le_one_div_of_le (by linarith [hwlog i])
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  have hv : w 0 - w N ≤ 2*Y/X := by
    have hh := reciprocal_log_variation (a:ℝ) ((a:ℝ)+N) ha0 hloga1 (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
    dsimp [w]
    simp only [Nat.cast_zero, add_zero]
    apply hh.trans
    apply (div_le_div_iff₀ ha0 hX0).2
    have hn : 0 ≤ (N:ℝ) := by positivity
    have hNY : (N:ℝ) ≤ Y := by linarith
    nlinarith
  let s : ℤ := -(n:ℤ)+((m2^2:ℕ):ℤ)+a
  let rlo : ℝ := -(n:ℝ)+(m2:ℝ)^2+(X-Y)
  let rhi : ℝ := -(n:ℝ)+(m2:ℝ)^2+X
  have heD : edgeDecay X Y b n m2 = min 1 (1/(b*(min |rlo| |rhi|+1))) := by
    unfold edgeDecay
    have hlo : (n:ℝ)-(m2:ℝ)^2-(X-Y) = -rlo := by dsimp [rlo]; ring
    have hhi : (n:ℝ)-(m2:ℝ)^2-X = -rhi := by dsimp [rhi]; ring
    rw [hlo, hhi, abs_neg, abs_neg]
  have hbound (r : ℝ) (k : ℤ) (hr : |r-(k:ℝ)| ≤ 1) (hd : min |rlo| |rhi| ≤ |r|) :
      |kernelPrimitive b k| ≤ 4 * edgeDecay X Y b n m2 := by
    apply (kernelPrimitive_near_bound b r k hb hb' hr).trans
    rw [heD]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply min_le_min_left
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) hb.le
  have hlo : |kernelPrimitive b (s-1)| ≤ 4 * edgeDecay X Y b n m2 := by
    apply hbound rlo (s-1) _ (min_le_left _ _)
    have he : rlo-((s-1:ℤ):ℝ) = X-Y-(a:ℝ)+1 := by dsimp [rlo,s]; push_cast; ring
    rw [he, abs_le]
    constructor <;> linarith
  have hhi : |kernelPrimitive b (s+N)| ≤ 4 * edgeDecay X Y b n m2 := by
    apply hbound rhi (s+N) _ (min_le_right _ _)
    have he : rhi-((s+N:ℤ):ℝ) = X-((a:ℝ)+N) := by dsimp [rhi,s]; push_cast; ring
    rw [he, abs_le]
    have hh : (a:ℝ)+(N:ℝ)+1 = (z:ℝ) := by exact_mod_cast hNz
    constructor <;> linarith
  have hh := kernel_weighted_range_bound b s w N hb hb' (fun i _ => hw i)
    (fun i _ => hwm i) (4*edgeDecay X Y b n m2) (by positivity) hlo hhi
  have hsum : innerSum X Y b n m2 = ∑ i ∈ Finset.range (N+1), w i * Kb b (s+i) := by
    unfold innerSum
    rw [Task556d.primeWindow_eq_Ico, Finset.sum_Ico_eq_sum_range]
    change (∑ i ∈ Finset.range (z-a), _) = _
    rw [hN]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [w,s]
    push_cast
    congr 2; ring
  rw [hsum]
  apply hh.trans
  have hcoeff : w N + w 0 ≤ 4/Real.log X := by
    calc
      _ ≤ 2/Real.log X + 2/Real.log X := add_le_add (hwL N) (hwL 0)
      _ = _ := by ring
  have hprod := mul_le_mul_of_nonneg_right hcoeff (by positivity : 0 ≤ 4*edgeDecay X Y b n m2)
  have he : 4/Real.log X * (4*edgeDecay X Y b n m2) = 16*(edgeDecay X Y b n m2 / Real.log X) := by ring
  rw [he] at hprod
  rw [mul_div_assoc] at hv
  nlinarith [div_nonneg he0 (by linarith : 0 ≤ Real.log X), div_nonneg hY.le hX0.le]

end LeanLab.KumchevLiu2007.Task687

namespace LeanLab.KumchevLiu2007.KernelSumSplit1122
open Real LeanLab.KumchevLiu2007 Task556a
open scoped BigOperators
/-- P0088 page 7 before display 27. The unchanged inner estimate follows from the
finite primitive and logarithmic weight variation, with constant 32. -/
theorem inner_window_bound :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ C X0 : ℝ, 0 < C ∧
      ∀ X : ℝ, X0 ≤ X → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B → ∀ n m2 : ℕ,
        m2 ∈ squareWindow (windowY X ε) →
        |innerSum X (windowY X ε) (bq X ε B q) n m2| ≤
          C * (edgeDecay X (windowY X ε) (bq X ε B q) n m2 / Real.log X + windowY X ε / X) := by
  intro B hB ε hε hε'
  have e1 : ∀ᶠ X : ℝ in Filter.atTop, 2 ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually_ge_atTop 2
  have e2 := (isLittleO_log_rpow_rpow_atTop (3*B)
    (by norm_num : (0:ℝ) < 7/12)).bound (by norm_num : (0:ℝ) < 1/2)
  have e3 : ∀ᶠ X : ℝ in Filter.atTop, 2 ≤ X ^ (5/12-ε/2) :=
    (tendsto_rpow_atTop (by linarith : (0:ℝ) < 5/12-ε/2)).eventually_ge_atTop 2
  obtain ⟨X1, hbig⟩ := Filter.eventually_atTop.mp (e1.and (e2.and e3))
  refine ⟨32, max 16 X1, by norm_num, ?_⟩
  intro X hX q hq1 hqP n m2 hm2
  have hX16 : 16 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  obtain ⟨hL, hsmall, hpow⟩ := hbig X ((le_max_right _ _).trans hX)
  let P : ℝ := Real.log X ^ B
  let Y : ℝ := windowY X ε
  have hL0 : 0 < Real.log X := by linarith
  have hP0 : 0 < P := Real.rpow_pos_of_pos hL0 _
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hX0 _
  have hYhalf : Y ≤ X/2 := by
    have he : Y * X ^ (5/12-ε/2) = X := by
      dsimp [Y, windowY]
      rw [← Real.rpow_add hX0]
      rw [show 7/12+ε/2+(5/12-ε/2) = (1:ℝ) by ring, Real.rpow_one]
    have hh := mul_le_mul_of_nonneg_left hpow hY0.le
    rw [he] at hh
    linarith
  have hYlo : X ^ (7/12:ℝ) ≤ Y := by
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hP3 : P ^ 3 = Real.log X ^ (3*B) := by
    dsimp [P]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    congr 1
    ring
  have hPY : P ^ 3 ≤ Y/2 := by
    rw [hP3]
    change ‖Real.log X ^ (3*B)‖ ≤ (1/2:ℝ) * ‖X ^ (7/12:ℝ)‖ at hsmall
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hL0 _), abs_of_pos (Real.rpow_pos_of_pos hX0 _)] at hsmall
    linarith
  have hq0 : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1' : (1:ℝ) ≤ q := by exact_mod_cast hq1
  have hbEq : bq X ε B q = P^3/((q:ℝ)*Y) := by
    dsimp [bq]
    change (Y * P ^ (-2:ℤ) / P)⁻¹ / q = _
    rw [zpow_neg, zpow_ofNat]
    field_simp
  have hb : 0 < bq X ε B q := by rw [hbEq]; positivity
  have hb' : bq X ε B q ≤ 1/2 := by
    rw [hbEq]
    apply (div_le_iff₀ (by positivity : 0 < (q:ℝ)*Y)).2
    nlinarith [mul_le_mul_of_nonneg_right hq1' hY0.le]
  exact Task687.inner_window_elementary X Y (bq X ε B q) n m2 hX16 hL hY0 hYhalf hb hb'

end LeanLab.KumchevLiu2007.KernelSumSplit1122

#print axioms LeanLab.KumchevLiu2007.Task687.Kb_even
#print axioms LeanLab.KumchevLiu2007.Task687.kernelPrimitive_step
#print axioms LeanLab.KumchevLiu2007.Task687.kernelPrimitive_bounded
#print axioms LeanLab.KumchevLiu2007.Task687.kernelPrimitive_decay
#print axioms LeanLab.KumchevLiu2007.Task687.kernelPrimitive_min_bound
#print axioms LeanLab.KumchevLiu2007.Task687.kernel_sum_range
#print axioms LeanLab.KumchevLiu2007.Task687.kernel_weighted_range
#print axioms LeanLab.KumchevLiu2007.Task687.kernel_weighted_range_bound
#print axioms LeanLab.KumchevLiu2007.Task687.kernelPrimitive_near_bound
#print axioms LeanLab.KumchevLiu2007.Task687.reciprocal_log_variation
#print axioms LeanLab.KumchevLiu2007.Task687.inner_window_elementary
#print axioms LeanLab.KumchevLiu2007.KernelSumSplit1122.inner_window_bound
