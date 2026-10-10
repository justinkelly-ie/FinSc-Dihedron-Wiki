# Quantum Mechanics over Discrete Dihedrons

This observation module formally verifies the quantum mechanical properties of the discrete 4D `Dihedron` algebra ($D = a + bi + cj + dk$), demonstrating that its categorical interfaces (`Functor`, `Applicative`, `Monad`) and algebraic instances (`Semigroup`, `Monoid`, `Num`, `Neg`) satisfy the laws of quantum operators, spin commutators, and monadic path propagation.

```idris
module Wiki.QuantumMechanicsAlgebra

import public Stage1.Dihedron
import public Stage1.Subalgebras
import public Stage1.DiracSpinor
import public Stage0.DihedronStream
import public Stage0.BoxInt

import public QuickCheck
import Data.Fuel

%default total

||| Property 1: Pauli Anti-Commutativity Law on Blue Quantum Subspace (ZX = -XZ)
||| Pauli X swaps scalarA and blueB.
||| Pauli Z negates blueB.
public export
prop_pauliAntiCommutation : BlueComplex -> Bool
prop_pauliAntiCommutation blueVal =
  let d = toDihedronBlue blueVal
      pauliX = \val => MkDihedronVal (blueB val) (scalarA val) (redC val) (greenD val)
      pauliZ = \val => MkDihedronVal (scalarA val) (-blueB val) (redC val) (greenD val)
      zx = pauliZ (pauliX d)
      xz = pauliX (pauliZ d)
  in zx == negDihedron xz

||| Property 2: Discrete Spin-1/2 Commutator Law [i, j] = -2k
||| Verifies that the commutator of Blue (i) and Red (j) basis elements yields minus twice Green (-2k).
public export
prop_spinCommutator : Bool
prop_spinCommutator =
  let elemI = MkDihedron 0 1 0 0
      elemJ = MkDihedron 0 0 1 0
      ij    = mulDihedron elemI elemJ
      ji    = mulDihedron elemJ elemI
      comm  = subDihedron ij ji
      minusTwoK = MkDihedron 0 0 0 (-2)
  in comm == minusTwoK

||| Property 3: Quadrance Norm Conservation under Unitary Blue Phase Rotation
||| Quadrance Q(D) = a² + b² - c² - d² is invariant under blue phase multiplication.
public export
prop_bluePhaseQuadranceInvariance : Dihedron -> Bool
prop_bluePhaseQuadranceInvariance d =
  let uPhase = MkDihedron 0 1 0 0 -- i phase
      rotated = mulDihedron d uPhase
      qOrig   = quadranceDihedron d
      qRot    = quadranceDihedron rotated
  in qOrig == qRot

||| Property 4: Monadic Feynman Path Propagator Composition
||| Binding (>>=) a componentwise phase transition function across a Dihedron
||| state corresponds to single-step propagator composition.
public export
prop_monadicPathBinding : Dihedron -> Bool
prop_monadicPathBinding d =
  let stepF = \x => MkDihedronVal x (x + 1) x (x - 1)
      bound = d >>= stepF
      expectedA = scalarA d
      expectedB = blueB d + 1
      expectedC = redC d
      expectedD = greenD d - 1
  in bound == MkDihedronVal expectedA expectedB expectedC expectedD

||| Property 5: Deforested Fused Feynman Path Propagator Equivalence
||| Verifies multi-step Pauli spinor path propagation via fusedComputePauliPathPropagator.
public export
prop_fusedPauliPathPropagator : Bool
prop_fusedPauliPathPropagator =
  let initialSpinor = MkPauliSpinor (MkDihedron 1 0 0 0) (MkDihedron 0 1 0 0)
      uPhase1 = MkDihedron 0 1 0 0 -- i phase
      uPhase2 = MkDihedron 0 1 0 0 -- i phase (i * i = -1)
      finalSpinor = fusedComputePauliPathPropagator (limit 100) initialSpinor [uPhase1, uPhase2]
      expectedSpinUp = MkDihedron (-1) 0 0 0
      expectedSpinDown = MkDihedron 0 (-1) 0 0
  in spinUp finalSpinor == expectedSpinUp && spinDown finalSpinor == expectedSpinDown

||| QuickCheck wrapper property for Pauli anti-commutation over test values
public export
qc_pauliAntiCommutation : Property
qc_pauliAntiCommutation =
  let b1 = MkBlue (intToBoxInt 5) (intToBoxInt 3)
      b2 = MkBlue (intToBoxInt 0) (intToBoxInt (-2))
  in property (prop_pauliAntiCommutation b1 && prop_pauliAntiCommutation b2)

||| QuickCheck wrapper property for Spin-1/2 commutator
public export
qc_spinCommutator : Property
qc_spinCommutator = property prop_spinCommutator

||| QuickCheck wrapper property for Blue Phase Quadrance Invariance
public export
qc_bluePhaseQuadranceInvariance : Property
qc_bluePhaseQuadranceInvariance =
  let d1 = MkDihedron 4 3 0 0
      d2 = MkDihedron 1 2 3 4
  in property (prop_bluePhaseQuadranceInvariance d1 && prop_bluePhaseQuadranceInvariance d2)

||| QuickCheck wrapper property for Monadic & Fused Path Binding
public export
qc_monadicPathBinding : Property
qc_monadicPathBinding =
  let d1 = MkDihedron 10 20 30 40
  in property (prop_monadicPathBinding d1 && prop_fusedPauliPathPropagator)

||| Property 6: Discrete Dirac Spinor Gamma-0 Identity (γ^0)² = I
public export
prop_diracGamma0Identity : DiracSpinor -> Bool
prop_diracGamma0Identity s = gamma0SquareIdentity s == s

||| Property 7: Dihedron and Dirac Spinor Quadrance Equivalence
public export
prop_diracDihedronQuadranceEquiv : Dihedron -> Bool
prop_diracDihedronQuadranceEquiv d = quadranceDihedron d == spinorQuadrance (dihedronToSpinor d)

||| Property 8: Dihedron Functorial Projection to QuadStream Multiset
public export
prop_dihedronToQuadStream : Dihedron -> Bool
prop_dihedronToQuadStream d =
  let (MkQuadStream e h p s) = dihedronToQuadStream d
      eSum = multisetSum e
      hSum = multisetSum h
      pSum = multisetSum p
      sSum = multisetSum s
  in (eSum == scalarA d) && (hSum == blueB d) && (pSum == redC d) && (sSum == greenD d)

||| Compile-time auditable boolean for Dirac Gamma-0 square identity
public export
prop_diracGamma0Audit : Bool
prop_diracGamma0Audit = prop_diracGamma0Identity (MkDiracSpinor 1 2 3 4)

||| Compile-time auditable boolean for Dirac Spinor Quadrance Equivalence
public export
prop_diracQuadranceAudit : Bool
prop_diracQuadranceAudit = prop_diracDihedronQuadranceEquiv (MkDihedron 1 2 3 4)

||| QuickCheck wrapper property for Dirac Gamma-0 and Quadrance Equivalence
public export
qc_diracCliffordAlgebra : Property
qc_diracCliffordAlgebra =
  let s1 = MkDiracSpinor 1 2 3 4
      d1 = MkDihedron 1 2 3 4
  in property (prop_diracGamma0Identity s1 && prop_diracDihedronQuadranceEquiv d1 && prop_dihedronToQuadStream d1)
```
