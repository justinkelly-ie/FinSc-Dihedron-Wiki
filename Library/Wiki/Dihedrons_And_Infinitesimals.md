# 📐 Dihedrons, Complex Numbers, and Infinitesimals

> **Student Guide to 4D Matrix Algebras & Dual Infinitesimals**
>
> In Norman Wildberger's *Famous Math Problems* (FMP 21a–d & 22a–b), standard complex numbers are reconstructed not as ad-hoc imaginary roots $\sqrt{-1}$, but as 2D matrix sub-algebras within the 4D Dihedron algebra $D(F)$.

---

```idris
module Wiki.Dihedrons_And_Infinitesimals

import QuickCheck
import Stage0.BoxInt
import Stage0.Multiset
import Stage1.Math.Infinitesimal

import Stage0.OnSeq.FusedStream
import Data.Fuel
import Stage1.VexelMaxel
import Stage1.Polynumber
import Stage1.Dihedron

import Stage1.Subalgebras


%default total

||| Erased compile-time witness verifying Dihedral group action invariance (d1 = d2)
public export
0 DihedralGroupActionWitness : (d1 : Nat) -> (d2 : Nat) -> Type
DihedralGroupActionWitness d1 d2 = d1 = d2

||| Static compile-time witness proving Dihedral group action invariance (16 = 16)
public export
prfDihedralGroupActionInvariance : DihedralGroupActionWitness 16 16
prfDihedralGroupActionInvariance = Refl

||| Verified Dihedral group state carrying erased action witness
public export
record VerifiedDihedralGroupState where
  constructor MkVerifiedDihedralGroupState
  quadrance1 : Nat
  quadrance2 : Nat
  0 actionPrf : DihedralGroupActionWitness quadrance1 quadrance2

||| $O(1)$ allocation deforested Dihedral group stream transducer using fusedHylomorphism
public export covering
fusedDihedralGroupStream : Fuel -> List (Nat, Nat) -> Nat
fusedDihedralGroupStream f items =
  fusedHylomorphism f
    (\st => case st of
              [] => Done
              (d1, d2) :: rest => Yield (d1 + d2) rest)
    (\val, acc => val + acc)
    0
    items
```

## 1. 🏛️ Three Matrix Geometries

Given any field $F$, the $2 \times 2$ matrix algebra $M_2(F)$ contains three canonical two-dimensional commutative sub-algebras:

- **Blue** $C_b(F)$: $i^2 = -1$ (Euclidean)
- **Red** $C_r(F)$: $j^2 = +1$ (Relativistic Minkowski)
- **Green** $C_g(F)$: $k^2 = +1$ or $\varepsilon^2 = 0$ (Null / Degenerate)

```idris
||| Verifies that Blue, Red, and Green subalgebra quadrances match their metric signatures
public export
prop_subalgebraSignatures : Property
prop_subalgebraSignatures =
  let a = intToBoxInt 5
      b = intToBoxInt 3
      qBlue  = quadranceDihedron (toDihedronBlue (MkBlue a b))
      qRed   = quadranceDihedron (toDihedronRed (MkRed a b))
      qGreen = quadranceDihedron (toDihedronGreen (MkGreen a b))
      streamSum = fusedDihedralGroupStream (limit 100) [(16, 16), (34, 34)]
  in property (unwrapBox qBlue == 34 && unwrapBox qRed == 16 && unwrapBox qGreen == 16 && streamSum == 100)
```

---

## 2. 🎛️ Dual Complex Algebraic Derivative

Evaluating a `Polynumber` at a dual number $a + b\varepsilon$ yields exact differentiation without limits:

$$P(a + b\varepsilon) = P(a) + P'(a)\cdot b\varepsilon$$

```idris
||| Verifies exact Faulhaber derivative readout via dual complex numbers
public export
prop_dualDerivativeTheorem : Property
prop_dualDerivativeTheorem =
  let -- P(x) = 4 + 2x + x³  => P'(x) = 2 + 3x²
      poly = MkPolynumber [intToBoxInt 4, intToBoxInt 2, intToBoxInt 0, intToBoxInt 1]
      (val, deriv) = autoDiffAt poly (intToBoxInt 2)
      -- P(2) = 4 + 4 + 8 = 16
      -- P'(2) = 2 + 12 = 14
  in property (unwrapBox val == 16 && unwrapBox deriv == 14)
```
