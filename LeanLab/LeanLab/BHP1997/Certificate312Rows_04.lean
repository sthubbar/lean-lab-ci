/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_256 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 256 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_257 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 257 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_258 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 258 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_259 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 259 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_260 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 260 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_261 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 261 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_262 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 262 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_263 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 263 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_264 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 264 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_265 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 265 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_266 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 266 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_267 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 267 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_268 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 268 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_269 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 269 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_270 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 270 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_271 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 271 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_272 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 272 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_273 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 273 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_274 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 274 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_275 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 275 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_276 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 276 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_277 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 277 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_278 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 278 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_279 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 279 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_280 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 280 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_281 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 281 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_282 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 282 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_283 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 283 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_284 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 284 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_285 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 285 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_286 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 286 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_287 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 287 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_288 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 288 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_289 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 289 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_290 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 290 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_291 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 291 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_292 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 292 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_293 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 293 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_294 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 294 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_295 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 295 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_296 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 296 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_297 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 297 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_298 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 298 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_299 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 299 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_300 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 300 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_301 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 301 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_302 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 302 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_303 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 303 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_304 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 304 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_305 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 305 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_306 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 306 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_307 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 307 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_308 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 308 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_309 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 309 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_310 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 310 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_311 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 311 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_312 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 312 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_313 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 313 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_314 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 314 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_315 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 315 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_316 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 316 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_317 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 317 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_318 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 318 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_319 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 319 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
/-- Page 51. Exact E2 row block 256 through 319. -/
theorem lowerTwo_rows312_04 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (256+i) j) = 0 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_256, lowerTwo_row_257, lowerTwo_row_258, lowerTwo_row_259, lowerTwo_row_260, lowerTwo_row_261, lowerTwo_row_262, lowerTwo_row_263, lowerTwo_row_264, lowerTwo_row_265, lowerTwo_row_266, lowerTwo_row_267, lowerTwo_row_268, lowerTwo_row_269, lowerTwo_row_270, lowerTwo_row_271, lowerTwo_row_272, lowerTwo_row_273, lowerTwo_row_274, lowerTwo_row_275, lowerTwo_row_276, lowerTwo_row_277, lowerTwo_row_278, lowerTwo_row_279, lowerTwo_row_280, lowerTwo_row_281, lowerTwo_row_282, lowerTwo_row_283, lowerTwo_row_284, lowerTwo_row_285, lowerTwo_row_286, lowerTwo_row_287, lowerTwo_row_288, lowerTwo_row_289, lowerTwo_row_290, lowerTwo_row_291, lowerTwo_row_292, lowerTwo_row_293, lowerTwo_row_294, lowerTwo_row_295, lowerTwo_row_296, lowerTwo_row_297, lowerTwo_row_298, lowerTwo_row_299, lowerTwo_row_300, lowerTwo_row_301, lowerTwo_row_302, lowerTwo_row_303, lowerTwo_row_304, lowerTwo_row_305, lowerTwo_row_306, lowerTwo_row_307, lowerTwo_row_308, lowerTwo_row_309, lowerTwo_row_310, lowerTwo_row_311, lowerTwo_row_312, lowerTwo_row_313, lowerTwo_row_314, lowerTwo_row_315, lowerTwo_row_316, lowerTwo_row_317, lowerTwo_row_318, lowerTwo_row_319, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
