---
declaration: theorem
origin: cited
---

# Box-Muller transform

CDIS id 98. If `U, V` are independent and uniform on `]0,1[`, then
 `X = √(-2 ln U) cos(2πV)` and `Y = √(-2 ln U) sin(2πV)` are independent standard normal
 variables. Plan: the map `(r, θ) ↦ (e^{-r²/2}, θ / 2π)` sends `]0,∞[ × ]0,2π[` onto
 `]0,1[²` with Jacobian `r e^{-r²/2} / 2π`, and composing with the Box-Muller map gives
 `polarCoord.symm`; `lintegral_comp_polarCoord_symm` then identifies the law with the
 standard Gaussian on `ℝ²`. Not formalized anywhere public (a `sorry` in
 sosudo/ppl-pralean).

## Depends on

No prerequisite in this chapter.

## Sources

- [Probabilités V, Box-Muller](../../sources/cdis-probabilites-v.md)
