import LeanLab.HeathBrownPuchta.Decomp1530Core215

/-! P0012 page 30 display 44. Existing private certificate checks moved verbatim. -/
namespace LeanLab.HeathBrownPuchta.Decomp1530c
open Finset Real LeanLab.HeathBrownPuchta.Decomp1530a LeanLab.HeathBrownPuchta.Decomp1530b
open LeanLab.Linnik
attribute [local instance 10] Classical.propDecidable
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open LeanLab.HeathBrownPuchta.Decomp1530c.CoreExports215

private lemma ckc32 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 32 + k.val) % 65536)
      (65536 - (512 * 32 + k.val) % 65536)) = rawI (512 * 32 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 32 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 32 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 32 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc33 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 33 + k.val) % 65536)
      (65536 - (512 * 33 + k.val) % 65536)) = rawI (512 * 33 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 33 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 33 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 33 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc34 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 34 + k.val) % 65536)
      (65536 - (512 * 34 + k.val) % 65536)) = rawI (512 * 34 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 34 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 34 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 34 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc35 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 35 + k.val) % 65536)
      (65536 - (512 * 35 + k.val) % 65536)) = rawI (512 * 35 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 35 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 35 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 35 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc36 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 36 + k.val) % 65536)
      (65536 - (512 * 36 + k.val) % 65536)) = rawI (512 * 36 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 36 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 36 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 36 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc37 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 37 + k.val) % 65536)
      (65536 - (512 * 37 + k.val) % 65536)) = rawI (512 * 37 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 37 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 37 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 37 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc38 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 38 + k.val) % 65536)
      (65536 - (512 * 38 + k.val) % 65536)) = rawI (512 * 38 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 38 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 38 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 38 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc39 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 39 + k.val) % 65536)
      (65536 - (512 * 39 + k.val) % 65536)) = rawI (512 * 39 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 39 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 39 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 39 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc40 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 40 + k.val) % 65536)
      (65536 - (512 * 40 + k.val) % 65536)) = rawI (512 * 40 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 40 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 40 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 40 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc41 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 41 + k.val) % 65536)
      (65536 - (512 * 41 + k.val) % 65536)) = rawI (512 * 41 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 41 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 41 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 41 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc42 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 42 + k.val) % 65536)
      (65536 - (512 * 42 + k.val) % 65536)) = rawI (512 * 42 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 42 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 42 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 42 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc43 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 43 + k.val) % 65536)
      (65536 - (512 * 43 + k.val) % 65536)) = rawI (512 * 43 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 43 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 43 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 43 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc44 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 44 + k.val) % 65536)
      (65536 - (512 * 44 + k.val) % 65536)) = rawI (512 * 44 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 44 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 44 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 44 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc45 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 45 + k.val) % 65536)
      (65536 - (512 * 45 + k.val) % 65536)) = rawI (512 * 45 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 45 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 45 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 45 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc46 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 46 + k.val) % 65536)
      (65536 - (512 * 46 + k.val) % 65536)) = rawI (512 * 46 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 46 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 46 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 46 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc47 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 47 + k.val) % 65536)
      (65536 - (512 * 47 + k.val) % 65536)) = rawI (512 * 47 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 47 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 47 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 47 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc48 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 48 + k.val) % 65536)
      (65536 - (512 * 48 + k.val) % 65536)) = rawI (512 * 48 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 48 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 48 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 48 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc49 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 49 + k.val) % 65536)
      (65536 - (512 * 49 + k.val) % 65536)) = rawI (512 * 49 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 49 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 49 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 49 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc50 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 50 + k.val) % 65536)
      (65536 - (512 * 50 + k.val) % 65536)) = rawI (512 * 50 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 50 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 50 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 50 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc51 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 51 + k.val) % 65536)
      (65536 - (512 * 51 + k.val) % 65536)) = rawI (512 * 51 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 51 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 51 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 51 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc52 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 52 + k.val) % 65536)
      (65536 - (512 * 52 + k.val) % 65536)) = rawI (512 * 52 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 52 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 52 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 52 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc53 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 53 + k.val) % 65536)
      (65536 - (512 * 53 + k.val) % 65536)) = rawI (512 * 53 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 53 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 53 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 53 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc54 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 54 + k.val) % 65536)
      (65536 - (512 * 54 + k.val) % 65536)) = rawI (512 * 54 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 54 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 54 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 54 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc55 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 55 + k.val) % 65536)
      (65536 - (512 * 55 + k.val) % 65536)) = rawI (512 * 55 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 55 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 55 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 55 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc56 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 56 + k.val) % 65536)
      (65536 - (512 * 56 + k.val) % 65536)) = rawI (512 * 56 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 56 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 56 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 56 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc57 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 57 + k.val) % 65536)
      (65536 - (512 * 57 + k.val) % 65536)) = rawI (512 * 57 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 57 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 57 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 57 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc58 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 58 + k.val) % 65536)
      (65536 - (512 * 58 + k.val) % 65536)) = rawI (512 * 58 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 58 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 58 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 58 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc59 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 59 + k.val) % 65536)
      (65536 - (512 * 59 + k.val) % 65536)) = rawI (512 * 59 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 59 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 59 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 59 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc60 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 60 + k.val) % 65536)
      (65536 - (512 * 60 + k.val) % 65536)) = rawI (512 * 60 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 60 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 60 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 60 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc61 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 61 + k.val) % 65536)
      (65536 - (512 * 61 + k.val) % 65536)) = rawI (512 * 61 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 61 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 61 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 61 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc62 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 62 + k.val) % 65536)
      (65536 - (512 * 62 + k.val) % 65536)) = rawI (512 * 62 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 62 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 62 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 62 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs

private lemma ckc63 : ∀ k : Fin 512,
    mcos (2 * 314159265358979323846 * min ((512 * 63 + k.val) % 65536)
      (65536 - (512 * 63 + k.val) % 65536)) = rawI (512 * 63 + k.val) := by
  have h : ∀ q : Fin 16, ∀ r : Fin 32,
    mcos (2 * 314159265358979323846 * min ((512 * 63 + (32 * q.val + r.val)) % 65536)
      (65536 - (512 * 63 + (32 * q.val + r.val)) % 65536)) = rawI (512 * 63 + (32 * q.val + r.val)) := by decide +kernel
  intro k
  have hq : k.val / 32 < 16 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 32)).2 k.isLt
  have hs := h ⟨k.val / 32, hq⟩ ⟨k.val % 32, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.div_add_mod] using hs


namespace CosB215Exports
export LeanLab.HeathBrownPuchta.Decomp1530c (ckc32 ckc33 ckc34 ckc35 ckc36 ckc37 ckc38 ckc39 ckc40 ckc41 ckc42 ckc43 ckc44 ckc45 ckc46 ckc47 ckc48 ckc49 ckc50 ckc51 ckc52 ckc53 ckc54 ckc55 ckc56 ckc57 ckc58 ckc59 ckc60 ckc61 ckc62 ckc63)
end CosB215Exports

end LeanLab.HeathBrownPuchta.Decomp1530c
