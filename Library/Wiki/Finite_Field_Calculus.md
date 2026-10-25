# 🔬 Infinitesimal Calculus over Finite Fields

> **Student Guide to Curve Geometry over $\mathbb{F}_p$ (FMP 22d)**
>
> Tangent lines and intersections are computed via the double-zero algebraic criterion, demonstrating exact calculus over modular fields without topology or limit operations.

---

```idris
module Wiki.Finite_Field_Calculus

import QuickCheck
import Stage0.BoxInt
import Stage0.Multiset
import Stage1.Math.Infinitesimal

import Stage1.Polynumber
import Stage1.Dihedron


%default total
```

## 1. 📐 Double Zero Criterion

```idris
||| Verifies tangent vector readout for semi-cubical parabola y² = x³ at a=2
public export
prop_tangentVectorReadout : Property
prop_tangentVectorReadout =
  let a = intToBoxInt 2
      -- x = α², y = α³ evaluated at a + 1*ε
      pX = MkPolynumber [intToBoxInt 0, intToBoxInt 0, intToBoxInt 1]
      pY = MkPolynumber [intToBoxInt 0, intToBoxInt 0, intToBoxInt 0, intToBoxInt 1]
      (valX, dx) = autoDiffAt pX a -- dx = 2a = 4
      (valY, dy) = autoDiffAt pY a -- dy = 3a² = 12
  in property (unwrapBox dx == 4 && unwrapBox dy == 12)
```
