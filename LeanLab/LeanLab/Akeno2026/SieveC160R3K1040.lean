/-
P0087 Akeno 2026 Appendix 5.1 page 36.
Grid 1/160 certificates. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.SieveCTables160Data
namespace LeanLab.Akeno2026.SieveFns.Grid160
theorem chk_c3_1040 : ∀ k < 1120, 1040 ≤ k → checks3 k := by
  unfold checks3
  decide +kernel
end LeanLab.Akeno2026.SieveFns.Grid160
